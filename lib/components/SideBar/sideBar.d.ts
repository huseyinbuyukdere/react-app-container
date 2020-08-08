/// <reference types="react" />
import { MenuItem } from '../../models';
interface SideBarProps {
    headerContent?: any;
    menu: MenuItem[];
    selectedRouteKey: any;
    footerContent?: any;
}
export default function SideBar(props: SideBarProps): JSX.Element;
export {};
