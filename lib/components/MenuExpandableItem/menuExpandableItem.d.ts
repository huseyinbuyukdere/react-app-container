/// <reference types="react" />
import { MenuItem as MenuItemContract } from '../../models';
interface MenuExpandableItemProps {
    label: string;
    onClick: (routeKey?: string) => void;
    iconComp?: any;
    iconName?: string;
    selectedRouteKey: string;
    subMenuItemList: MenuItemContract[];
}
declare const MenuExpandableItem: (props: MenuExpandableItemProps) => JSX.Element;
export default MenuExpandableItem;
