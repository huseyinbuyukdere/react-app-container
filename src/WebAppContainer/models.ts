export interface ContainerRoute {
    path: string
    key: string
    label: string
    component: any
    exact?: boolean
}

export interface MenuItem {
    label: string
    routeKey?: string
    iconName?: string
    iconComp?: any
    onClick?: (routeKey?: string,path?:string) => void
    subMenuItemList?: MenuItem[]
}

export interface DesignConfig {
    headerMenu?: MenuItem[]
    sideBarMenu?: MenuItem[]
    sideBarHeaderContent?: React.ReactElement | string
    sideBarFooterContent?: React.ReactElement | string
    headerLeftContent?: React.ReactElement | string
    headerRightContent?: React.ReactElement | string
}
